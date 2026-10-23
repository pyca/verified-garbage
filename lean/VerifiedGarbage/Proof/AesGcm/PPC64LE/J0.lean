module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Tag
public import VerifiedGarbage.Proof.AesGcm.J0Words
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Gcm.Short
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.Gather.PPC64LE.Copy
import VerifiedGarbage.Proof.Poly1305.PPC64LE.Buffer

/-!
# AES-GCM on PPC64LE: the streaming state for a nonce (`j0`)

Untrusted: everything here is checked by Lean. `j0` writes `J₀` for the
`L`-byte nonce at `N` (`r18`, `r19`) to `St` (`j0core_wp`): a 12-byte nonce
and `0x00000001` (`j012`), or GHASH of the nonce padded and of the lengths
block of no additional data and the nonce (`j0hash`, by `absorb`, `flush`
and `lens` with the accumulator at `St`). `initState` then writes the first
counter block `inc₃₂(J₀)` to `St + 48`, its last word read byte-reversed
and incremented (`inc32_words`), and zeroes the accumulator at `St + 16`
(`initState_wp`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.Impl.AesGcm.PPC64LE VG.WriteBytes VG.Proof.Gcm
open VG.PPC64LE hiding wp_add wp_addi wp_and wp_ld wp_li wp_lsl wp_lsr wp_lwz wp_std wp_stw wp_sub wp_subi
  wp_xor wp_lwbrx wp_stwbrx
open VG.Proof.ChaCha20Poly1305.PPC64LE (wp_addi wp_subi wp_li wp_lis wp_and wp_ld wp_std wp_lwz wp_stw)
open VG.Proof.Gather.PPC64LE (eval_zero)
open VG.Spec.Gcm (Block blockAt ghashFrom ofBytes inc32 zeros padLen)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le4)
open VG.Proof.AesGcm (inc32_words ofBytes_le4)

theorem rev32_eq (w : BitVec 32) : rev32 w = byteRev32 w := rfl

/-- `stwbrx` of `lwbrx` plus one: the word incremented, big-endian. -/
theorem inc_word (w : BitVec 32) :
    rev32 (((rev32 w).setWidth 64 + BitVec.ofNat 64 1).setWidth 32) = byteRev32 (byteRev32 w + 1) := by
  rw [rev32_eq, rev32_eq, BitVec.setWidth_add _ _ (by decide : 32 ≤ 64),
    BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
  rfl

/-- The block at `p` from its four words. -/
theorem blockAt_words (m : Mem) (p : Addr) :
    blockAt m p = byteRev32 (m.readW p 32) ++ byteRev32 (m.readW (p + BitVec.ofNat 64 4) 32) ++
      byteRev32 (m.readW (p + BitVec.ofNat 64 8) 32) ++ byteRev32 (m.readW (p + BitVec.ofNat 64 12) 32) := by
  rw [← Proof.AesGcm.ofBytes_le4, Cmac.le4_readW, Cmac.le4_readW, Cmac.le4_readW, Cmac.le4_readW]
  simp only [blockAt]
  congr 1
  rw [show (16 : Nat) = 4 + 12 from rfl, ← bytesAt_split, show (12 : Nat) = 4 + 8 from rfl,
    ← bytesAt_split, show (8 : Nat) = 4 + 4 from rfl, ← bytesAt_split, add_ofNat_add, add_ofNat_add]
  simp only [List.append_assoc, Nat.reduceAdd]

/-- What `initState` does. -/
structure InitPost (s₀ : State) (St : Addr) (s : State) : Prop where
  pk : PK s₀ s
  frame : Frame [⟨St + BitVec.ofNat 64 16, 16⟩, ⟨St + BitVec.ofNat 64 48, 16⟩] s₀.mem s.mem
  j0 : blockAt s.mem St = blockAt s₀.mem St
  y : blockAt s.mem (St + BitVec.ofNat 64 16) = 0
  cb : blockAt s.mem (St + BitVec.ofNat 64 48) = inc32 (blockAt s₀.mem St)

theorem initState_wp {s : State} {W St C : Addr} (he : Env s W St C) :
    WP isa (.block initState) s (InitPost s St) := by
  unfold initState
  refine wp_ld (a := St + BitVec.ofNat 64 0) (by decide) (by decide) (by rw [he.r15])
    (he.stRdR (by decide)) fun s₁ u₁ => ?_
  refine wp_std (a := St + BitVec.ofNat 64 48) (by decide) (by decide)
    (by rw [u₁.other _ (by decide), he.r15]) (by rw [u₁.wr]; exact he.stInR (n := 8) (by decide))
    fun s₂ u₂ => ?_
  refine wp_lwz (a := St + BitVec.ofNat 64 8) (by decide) (by decide)
    (by rw [u₂.gpr, u₁.other _ (by decide), he.r15])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact he.stRdR (by decide)) fun s₃ u₃ => ?_
  refine wp_stw (a := St + BitVec.ofNat 64 56) (by decide) (by decide)
    (by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), he.r15])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact he.stInR (n := 4) (by decide)) fun s₄ u₄ => ?_
  refine wp_li (by decide) fun s₅ u₅ => ?_
  refine wp_lwbrx (ea := St + BitVec.ofNat 64 12) (by decide)
    (by rw [u₅.gpr, u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide),
      he.r15])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]
        exact he.stRdR (by decide)) fun s₆ u₆ => ?_
  refine wp_addi (by decide) (by decide) fun s₇ u₇ => wp_li (by decide) fun s₈ u₈ => ?_
  have pk₈ : PK s s₈ := (PK.ofUpd u₁).trans ((PK.ofMupd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofMupd u₄).trans
    ((PK.ofUpd u₅).trans ((PK.ofUpd u₆).trans ((PK.ofUpd u₇).trans (PK.ofUpd u₈)))))))
  have r15₈ : s₈.gpr .r15 = St := by rw [pk₈.gpr .r15 (by decide), he.r15]
  refine wp_stwbrx (ea := St + BitVec.ofNat 64 60) (by decide) (by rw [r15₈, u₈.gpr])
    (by rw [pk₈.wr]; exact he.stInR (n := 4) (by decide)) fun s₉ u₉ => ?_
  refine wp_li (by decide) fun s₁₀ u₁₀ => ?_
  refine wp_std (a := St + BitVec.ofNat 64 16) (by decide) (by decide)
    (by rw [u₁₀.other _ (by decide), u₉.gpr, r15₈])
    (by rw [u₁₀.wr, u₉.wr, pk₈.wr]; exact he.stInR (n := 8) (by decide)) fun s₁₁ u₁₁ => ?_
  refine wp_std (a := St + BitVec.ofNat 64 24) (by decide) (by decide)
    (by rw [u₁₁.gpr, u₁₀.other _ (by decide), u₉.gpr, r15₈])
    (by rw [u₁₁.wr, u₁₀.wr, u₉.wr, pk₈.wr]; exact he.stInR (n := 8) (by decide)) fun s₁₂ u₁₂ =>
    WP.block_nil ?_
  have r5 : s₁.gpr .r5 = s.mem.readW St 64 := by rw [u₁.gpr, BitVec.add_zero]
  have m₂ : s₂.mem = s.mem.writeW (St + BitVec.ofNat 64 48) (s.mem.readW St 64) := by
    rw [u₂.mem, r5, u₁.mem]
  have m₄ : s₄.mem = s₂.mem.writeW (St + BitVec.ofNat 64 56)
      (((s₂.mem.readW (St + BitVec.ofNat 64 8) 32).setWidth 64).setWidth 32) := by
    rw [u₄.mem, u₃.gpr, u₃.mem]
  have m₈ : s₈.mem = s₄.mem := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem]
  have r8 : s₈.gpr .r8 = (rev32 (s₄.mem.readW (St + BitVec.ofNat 64 12) 32)).setWidth 64 + BitVec.ofNat 64 1 := by
    rw [u₈.other _ (by decide), u₇.gpr, u₆.gpr, u₅.mem]
  generalize hX : Spec.Aes.bytesAt s.mem St 12 ++
    le4 (byteRev32 (byteRev32 (s.mem.readW (St + BitVec.ofNat 64 12) 32) + 1)) = X
  have hXl : X.length = 16 := by
    rw [← hX, List.length_append, Proof.AesGcm.length_bytesAt, Cmac.length_le4]
  have m₉ : s₉.mem = writeBytes s.mem (St + BitVec.ofNat 64 48) X := by
    rw [u₉.mem, r8, inc_word, m₈, m₄, m₂, ← hX]; exact Proof.AesGcm.initMem_eq _ _
  have hm : s₁₂.mem = writeBytes (writeBytes s.mem (St + BitVec.ofNat 64 48) X) (St + BitVec.ofNat 64 16)
      (zeros 16) := by
    rw [u₁₂.mem, u₁₁.gpr, u₁₁.mem, u₁₀.gpr, u₁₀.mem, m₉,
      show St + BitVec.ofNat 64 24 = St + BitVec.ofNat 64 16 + BitVec.ofNat 64 8 from (Offset.add_add St 16 8).symm]
    exact Proof.AesGcm.write_zeros16 _ _
  have hz : (zeros 16).length = 16 := Proof.Gcm.length_zeros 16
  have hf₁ : Frame [⟨St + BitVec.ofNat 64 16, 16⟩] (writeBytes s.mem (St + BitVec.ofNat 64 48) X) s₁₂.mem := by
    rw [hm]; exact Proof.AesGcm.writeBytes_frame' _ hz
  have hf₀ : Frame [⟨St + BitVec.ofNat 64 48, 16⟩] s.mem (writeBytes s.mem (St + BitVec.ofNat 64 48) X) :=
    Proof.AesGcm.writeBytes_frame' _ hXl
  refine ⟨pk₈.trans ((PK.ofMupd u₉).trans ((PK.ofUpd u₁₀).trans ((PK.ofMupd u₁₁).trans (PK.ofMupd u₁₂)))),
    (hf₀.mono (by simp)).trans (hf₁.mono (by simp)), ?_, ?_, ?_⟩
  · simp only [blockAt]
    rw [Cmac.bytesAt_frame16 hf₁ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]
        exact Offset.base_disjoint St (by omega) (by omega)),
      Cmac.bytesAt_frame16 hf₀ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]
        exact Offset.base_disjoint St (by omega) (by omega))]
  · have h := Proof.AesGcm.bytesAt_writeBytes_self (writeBytes s.mem (St + BitVec.ofNat 64 48) X)
      (St + BitVec.ofNat 64 16) (zeros 16) (by rw [hz]; omega)
    rw [hz, ← hm] at h
    simp only [blockAt]; rw [h, Proof.Gcm.ofBytes_zeros16]
  · have h := Proof.AesGcm.bytesAt_writeBytes_self s.mem (St + BitVec.ofNat 64 48) X (by rw [hXl]; omega)
    rw [hXl] at h
    have h8 : Spec.Aes.bytesAt s.mem (St + BitVec.ofNat 64 4) 8 = Spec.Aes.bytesAt s.mem (St + BitVec.ofNat 64 4) 4 ++
        Spec.Aes.bytesAt s.mem (St + BitVec.ofNat 64 4 + BitVec.ofNat 64 4) 4 :=
      Proof.AesGcm.bytesAt_add _ _ 4 4
    have h12 : Spec.Aes.bytesAt s.mem St 12 = Spec.Aes.bytesAt s.mem St 4 ++
        Spec.Aes.bytesAt s.mem (St + BitVec.ofNat 64 4) 8 :=
      Proof.AesGcm.bytesAt_add _ _ 4 8
    simp only [blockAt]
    rw [Cmac.bytesAt_frame16 hf₁ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]
        exact Offset.disjoint St (by omega) (by omega) (by omega)), h, ← hX,
      ← blockAt, blockAt_words s.mem St, inc32_words,
      ← Cmac.byteRev32_byteRev32 (byteRev32 (s.mem.readW (St + BitVec.ofNat 64 12) 32) + 1),
      ← ofBytes_le4, Cmac.le4_readW, Cmac.le4_readW, Cmac.le4_readW, h12, h8, Offset.add_add]
    simp only [List.append_assoc, Nat.reduceAdd, Cmac.byteRev32_byteRev32]

/-- Before `j0`: the `n`-byte nonce at `N` (`r18`, `r19`). -/
structure J0In (s : State) (W St C N : Addr) (n : Nat) : Prop where
  env : Env s W St C
  r18 : s.gpr .r18 = N
  r19 : s.gpr .r19 = BitVec.ofNat 64 n
  rd : Covers [⟨N, n⟩] (s.rd ++ s.wr)
  dst : (⟨N, n⟩ : Region).Disjoint (stR St)
  dw : (⟨N, n⟩ : Region).Disjoint ⟨W, 2560⟩
  fit : N.toNat + n ≤ 2 ^ 64
  lt : n < 2 ^ 64

/-- What `j0` keeps: what a piece keeps but `r21` and `r22`. -/
def j0Keep : List Reg := [.r2, .r14, .r15, .r16, .r17, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31]

structure J0K (s s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  gpr : ∀ r ∈ j0Keep, s'.gpr r = s.gpr r

theorem J0K.trans {s t u : State} (h₁ : J0K s t) (h₂ : J0K t u) : J0K s u :=
  ⟨h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp,
    fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr)⟩

theorem j0Keep_keep : ∀ r ∈ j0Keep, r ∈ keepRegs := by decide

theorem J0K.ofPK {s t : State} (h : PK s t) : J0K s t :=
  ⟨h.rd, h.wr, h.sp, fun r hr => h.gpr r (j0Keep_keep r hr)⟩

theorem J0K.ofUpd {s t : State} {d : Reg} {v : BitVec 64} (u : Proof.ChaCha20Poly1305.PPC64LE.Upd s t d v)
    (hd : d ∉ j0Keep := by decide) : J0K s t :=
  ⟨u.rd, u.wr, u.sp, fun r hr => u.other r fun h => hd (h ▸ hr)⟩

theorem Env.of_j0k {s t : State} {W St C : Addr} (h : Env s W St C) (k : J0K s t) : Env t W St C where
  r14 := by rw [k.gpr .r14 (by decide), h.r14]
  r15 := by rw [k.gpr .r15 (by decide), h.r15]
  r16 := by rw [k.gpr .r16 (by decide), h.r16]
  wW := by rw [k.wr]; exact h.wW
  wSt := by rw [k.wr]; exact h.wSt
  rC := by rw [k.rd, k.wr]; exact h.rC
  cw := h.cw
  cs := h.cs
  sw := h.sw
  wfit := h.wfit
  sfit := h.sfit
  cfit := h.cfit

/-- `J₀` of the nonce `iv` at `St`. -/
structure J0Mid (s₀ : State) (W St C : Addr) (iv : List Byte) (s : State) : Prop where
  kp : J0K s₀ s
  frame : Frame (pieceRs W St) s₀.mem s.mem
  j0 : blockAt s.mem St = Spec.Gcm.j0 (hk s₀.mem C) iv

theorem lis_one : (((0x0100 : BitVec 16) ++ (0 : BitVec 16)).signExtend 64).setWidth 32 =
    BitVec.ofNat 32 0x01000000 := by decide

/-- `J₀` of a 12-byte nonce. -/
theorem j012_wp {s : State} {W St C N : Addr} (h : J0In s W St C N 12) :
    WP isa (.block j012) s (J0Mid s W St C (bytesAt s.mem N 12)) := by
  have he := h.env
  have inN : ∀ {d k : Nat}, d + k ≤ 12 → InRegions (s.rd ++ s.wr) (N + BitVec.ofNat 64 d) k := fun hd =>
    VG.Proof.Gather.PPC64LE.covers_off h.rd hd (by decide) _ _
      ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  unfold j012
  refine wp_ld (a := N) (by decide) (by decide) (by rw [h.r18]; exact BitVec.add_zero _)
    (by simpa only [BitVec.add_zero] using inN (d := 0) (k := 8) (by decide)) fun s₁ u₁ => ?_
  refine wp_lwz (a := N + BitVec.ofNat 64 8) (by decide) (by decide) (by rw [u₁.other _ (by decide), h.r18])
    (by rw [u₁.rd, u₁.wr]; exact inN (by decide)) fun s₂ u₂ => ?_
  refine wp_lis fun s₃ u₃ => ?_
  refine wp_std (a := St) (by decide) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), he.r15]
        exact BitVec.add_zero _)
    (by rw [u₃.wr, u₂.wr, u₁.wr]; simpa only [BitVec.add_zero] using he.stInR (d := 0) (n := 8) (by decide))
    fun s₄ u₄ => ?_
  refine wp_stw (a := St + BitVec.ofNat 64 8) (by decide) (by decide)
    (by rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), he.r15])
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact he.stInR (by decide)) fun s₅ u₅ => ?_
  refine wp_stw (a := St + BitVec.ofNat 64 12) (by decide) (by decide)
    (by rw [u₅.gpr, u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), he.r15])
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact he.stInR (by decide)) fun s₆ u₆ => WP.block_nil ?_
  have hm : s₆.mem = writeBytes s.mem St (bytesAt s.mem N 12 ++ [0, 0, 0, 1]) := by
    rw [u₆.mem, u₅.mem, u₄.mem, u₅.gpr, u₄.gpr, u₃.gpr, lis_one, u₃.other .r6 (by decide),
      u₃.other .r5 (by decide), u₂.gpr, u₂.other .r5 (by decide), u₁.gpr, u₃.mem, u₂.mem, u₁.mem,
      BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
    exact Proof.AesGcm.j012Mem_eq _ _ _
  have hl : (bytesAt s.mem N 12 ++ [0, 0, 0, 1]).length = 16 := by
    rw [List.length_append, Proof.AesGcm.length_bytesAt]; rfl
  refine ⟨J0K.ofPK ((PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofMupd u₄).trans
    ((PK.ofMupd u₅).trans (PK.ofMupd u₆)))))), ?_, ?_⟩
  · rw [hm]
    exact (Proof.AesGcm.writeBytes_frame' _ hl).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
  · have hb := Proof.AesGcm.bytesAt_writeBytes_self s.mem St (bytesAt s.mem N 12 ++ [0, 0, 0, 1])
      (by rw [hl]; omega)
    rw [hl] at hb
    simp only [blockAt]
    rw [hm, hb, j0_12 _ (Proof.AesGcm.length_bytesAt _ _ _)]

/-- Frames within the pieces' regions compose. -/
theorem frame_abs {W St : Addr} {m m' : Mem} (h : Frame (absRs W St 0) m m') : Frame (pieceRs W St) m m' :=
  h.sub (absRs_pieces (by decide))

theorem frame_gh {W St : Addr} {m m' : Mem} (h : Frame (ghRs W St 0) m m') : Frame (pieceRs W St) m m' :=
  frame_abs (h.sub ghRs_abs)

/-- `J₀` of a nonce of any length but 12. -/
theorem j0hash_wp {s : State} {W St C N : Addr} {n : Nat} (h : J0In s W St C N n) (hn : n ≠ 12) :
    WP isa j0hash s (J0Mid s W St C (bytesAt s.mem N n)) := by
  have he := h.env
  unfold j0hash
  refine WP.seq (wp_li (by decide) fun s₁ u₁ => ?_)
  refine wp_std (a := St) (by decide) (by decide)
    (by rw [u₁.other _ (by decide), he.r15]; exact BitVec.add_zero _)
    (by rw [u₁.wr]; simpa only [BitVec.add_zero] using he.stInR (d := 0) (n := 8) (by decide)) fun s₂ u₂ => ?_
  refine wp_std (a := St + BitVec.ofNat 64 8) (by decide) (by decide)
    (by rw [u₂.gpr, u₁.other _ (by decide), he.r15])
    (by rw [u₂.wr, u₁.wr]; exact he.stInR (by decide)) fun s₃ u₃ => ?_
  refine wp_mv fun s₄ u₄ => wp_li (by decide) fun s₅ u₅ => WP.block_nil ?_
  have pk₅ : J0K s s₅ := (J0K.ofPK ((PK.ofUpd u₁).trans ((PK.ofMupd u₂).trans (PK.ofMupd u₃)))).trans
    ((J0K.ofUpd u₄).trans (J0K.ofUpd u₅))
  have hm₅ : s₅.mem = writeBytes s.mem St (zeros 16) := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.gpr, u₂.mem, u₁.mem, u₁.gpr]
    exact Proof.AesGcm.write_zeros16 _ _
  have hz : (zeros 16).length = 16 := length_zeros 16
  have f₅' : Frame [⟨St, 16⟩] s.mem s₅.mem := by rw [hm₅]; exact Proof.AesGcm.writeBytes_frame' _ hz
  have f₅ : Frame (pieceRs W St) s.mem s₅.mem :=
    f₅'.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
  have hiv₅ : bytesAt s₅.mem N n = bytesAt s.mem N n :=
    Cmac.bytesAt_frame f₅' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact h.dst.sub_right (Region.sub_prefix (by decide))) (by have := h.lt; omega)
  have hY₅ : blockAt s₅.mem (yA St 0) = 0 := by
    have hb := Proof.AesGcm.bytesAt_writeBytes_self s.mem St (zeros 16) (by rw [hz]; omega)
    rw [hz] at hb
    simp only [blockAt, yA, BitVec.add_zero]
    rw [hm₅, hb, ofBytes_zeros16]
  have r22₅ : s₅.gpr .r22 = BitVec.ofNat 64 n := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.gpr, u₁.other _ (by decide), h.r19]
  have hp : AbsPre s₅ W St C 0 N n [] :=
    { env := he.of_j0k pk₅
      hyo := .inl rfl
      r18 := by
        rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), h.r18]
      r19 := by
        rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), h.r19]
      r20 := by rw [u₅.gpr]; rfl
      abs := absorbed_nil _ hY₅
      rd := by rw [pk₅.rd, pk₅.wr]; exact h.rd
      dst := h.dst
      dw := h.dw
      fit := h.fit
      lt := h.lt }
  refine WP.seq (WP.mono (absorb_wp hp) fun s₆ a₆ => ?_)
  have ab₆ := a₆.abs
  rw [List.nil_append, hiv₅] at ab₆
  generalize hiv : bytesAt s.mem N n = iv at ab₆
  have hl : iv.length = n := by rw [← hiv]; exact Proof.AesGcm.length_bytesAt _ _ _
  have f₆ : Frame (pieceRs W St) s.mem s₆.mem := f₅.trans (frame_abs a₆.frame)
  refine WP.seq (wp_li (by decide) fun s₇ u₇ => wp_and fun s₈ u₈ => WP.block_nil ?_)
  have pk₅₈ : PK s₅ s₈ := a₆.pk.trans ((PK.ofUpd u₇).trans (PK.ofUpd u₈))
  have hk₈ : hk s₈.mem C = hk s.mem C := by
    rw [u₈.mem, u₇.mem]; exact hk_keep he f₆
  have hk₅ : hk s₅.mem C = hk s.mem C := hk_keep he f₅
  have r22₈ : s₈.gpr .r22 = BitVec.ofNat 64 n := by
    rw [pk₅₈.gpr .r22 (by decide), r22₅]
  have hq : FlPre s₈ W St C 0 iv :=
    { env := (he.of_j0k pk₅).of_pk pk₅₈
      hyo := .inl rfl
      r20 := by
        rw [u₈.gpr, u₇.gpr, u₇.other _ (by decide), a₆.pk.gpr .r22 (by decide), r22₅, hl]
        exact ofNat_and15 h.lt
      abs := by rw [hk₈, u₈.mem, u₇.mem, ← hk₅]; exact ab₆ }
  refine WP.seq (WP.mono (flush_wp hq) fun s₉ g₉ => ?_)
  refine WP.seq (wp_li (by decide) fun s₁₀ u₁₀ => WP.block_nil ?_)
  have pk₁₀ : J0K s s₁₀ := pk₅.trans ((J0K.ofPK (pk₅₈.trans g₉.pk)).trans (J0K.ofUpd u₁₀))
  have f₁₀ : Frame (pieceRs W St) s.mem s₁₀.mem := by
    rw [u₁₀.mem]; exact f₆.trans (by rw [← u₇.mem, ← u₈.mem]; exact frame_gh g₉.frame)
  have hr : LensPre s₁₀ W St C 0 0 n :=
    { env := he.of_j0k pk₁₀
      hyo := .inl rfl
      r21 := u₁₀.gpr
      r22 := by rw [u₁₀.other _ (by decide), g₉.pk.gpr .r22 (by decide), pk₅₈.gpr .r22 (by decide), r22₅]
      ha := by decide
      hc := h.lt }
  refine WP.mono (lens_wp hr) fun s₁₁ l₁₁ => ?_
  have f₁₁ : Frame (pieceRs W St) s.mem s₁₁.mem := f₁₀.trans (frame_gh l₁₁.frame)
  refine ⟨pk₁₀.trans (J0K.ofPK l₁₁.pk), f₁₁, ?_⟩
  have hY := l₁₁.y
  have hw := g₉.abs.whole_eq (by rw [List.length_append, length_zeros]; exact length_pad_mod _)
  rw [hk_keep he f₁₀, u₁₀.mem, hw, hk₈] at hY
  simp only [yA, BitVec.add_zero] at hY
  rw [hY, j0_eq _ (by rw [hl]; exact hn), hl]

/-- After `j0`: `J₀`, the accumulator zeroed and the first counter block. -/
structure J0Out (s₀ : State) (W St C : Addr) (iv : List Byte) (s : State) : Prop where
  kp : J0K s₀ s
  frame : Frame (pieceRs W St) s₀.mem s.mem
  j0 : blockAt s.mem St = Spec.Gcm.j0 (hk s₀.mem C) iv
  y : blockAt s.mem (St + BitVec.ofNat 64 16) = 0
  cb : blockAt s.mem (St + BitVec.ofNat 64 48) = inc32 (Spec.Gcm.j0 (hk s₀.mem C) iv)

theorem sub12_zero {n : Nat} (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n - BitVec.ofNat 64 12 == 0) = decide (n = 12) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro h
    have h' : BitVec.ofNat 64 n = BitVec.ofNat 64 12 := by
      rw [← BitVec.sub_add_cancel (BitVec.ofNat 64 n) (BitVec.ofNat 64 12), h]; decide
    have := congrArg BitVec.toNat h'
    rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
      Nat.mod_eq_of_lt (by decide : 12 < 2 ^ 64)] at this
  · rintro rfl; rfl

theorem j0_wp {s : State} {W St C N : Addr} {n : Nat} (h : J0In s W St C N n) :
    WP isa j0 s (J0Out s W St C (bytesAt s.mem N n)) := by
  unfold j0
  refine WP.seq (wp_subi (by decide) (by decide) fun s₁ u₁ => WP.block_nil ?_)
  have k₁ : PK s s₁ := PK.ofUpd u₁
  have h₁ : J0In s₁ W St C N n :=
    { env := h.env.of_pk k₁
      r18 := by rw [u₁.other _ (by decide), h.r18]
      r19 := by rw [u₁.other _ (by decide), h.r19]
      rd := by rw [k₁.rd, k₁.wr]; exact h.rd
      dst := h.dst
      dw := h.dw
      fit := h.fit
      lt := h.lt }
  have hiv : bytesAt s₁.mem N n = bytesAt s.mem N n := by rw [u₁.mem]
  have hk₁ : hk s₁.mem C = hk s.mem C := by rw [u₁.mem]
  refine WP.seq (WP.mono (Q := J0Mid s₁ W St C (bytesAt s.mem N n)) ?_ fun s₂ m₂ =>
    WP.mono (initState_wp (h.env.of_j0k ((J0K.ofPK k₁).trans m₂.kp))) fun s₃ i₃ => ?_)
  · refine WP.ite (decide (n = 12))
      (by rw [VG.Proof.Poly1305.PPC64LE.eval_zero, u₁.gpr, h.r19, sub12_zero h.lt]) (fun ht => ?_) (fun hf => ?_)
    · have h12 : n = 12 := of_decide_eq_true ht
      subst h12
      rw [← hiv]; exact j012_wp h₁
    · rw [← hiv]; exact j0hash_wp h₁ (by simpa using hf)
  · have f₂ : Frame (pieceRs W St) s.mem s₂.mem := by
      have := m₂.frame; rwa [u₁.mem] at this
    refine ⟨(J0K.ofPK k₁).trans (m₂.kp.trans (J0K.ofPK i₃.pk)), f₂.trans (i₃.frame.sub fun r hr => ?_),
      i₃.j0.trans (by rw [m₂.j0, hk₁]), i₃.y, i₃.cb.trans (by rw [m₂.j0, hk₁])⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact sub_st (by decide) W

end VG.Proof.AesGcm.PPC64LE
