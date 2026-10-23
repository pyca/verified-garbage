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

end

end VG.Proof.AesGcm.PPC64LE
