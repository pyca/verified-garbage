module

public import VerifiedGarbage.Proof.MdStream.X86_64.PadExec
public import VerifiedGarbage.Impl.Pbkdf2.Md.X86_64
public import VerifiedGarbage.Proof.Pbkdf2.X86_64.Copy
public import VerifiedGarbage.Proof.Pbkdf2.MdStep
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Block
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# HMAC over any Merkle–Damgård hash function on x86-64: the outer block

What `blkV` (`Impl/Pbkdf2/Md/X86_64.lean`) writes: the inner digest and
the padding of a `B + D`-byte message, 16 bytes at a time.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.X86_64.Blk

open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Proof.MdStream.X86_64
open VG.Impl.MdStream.X86_64 (at_)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.X86_64 (ea_off)
open VG.Proof.MdStream (Md)
open VG.Spec.Sha256 (bytesAt)

/-- Four dwords, each moved into an SSE register (`movq`), interleaved by
`punpckldq` and `punpcklqdq`. -/
theorem vec4 (w0 w1 w2 w3 : BitVec 32) :
    XBinOp.eval .punpcklqdq
      (XBinOp.eval .punpckldq ((0 : BitVec 64) ++ w0.setWidth 64) ((0 : BitVec 64) ++ w1.setWidth 64))
      (XBinOp.eval .punpckldq ((0 : BitVec 64) ++ w2.setWidth 64) ((0 : BitVec 64) ++ w3.setWidth 64)) =
      (w3 ++ w2) ++ (w1 ++ w0) := by
  have a : ∀ w : BitVec 32, dword ((0 : BitVec 64) ++ w.setWidth 64) 0 = w := fun w => by
    ext i hi; simp only [dword, BitVec.getElem_extractLsb']; rw [BitVec.getLsbD_append]
    simp [show i < 64 by omega, BitVec.getLsbD_eq_getElem hi]
  have b : ∀ w : BitVec 32, dword ((0 : BitVec 64) ++ w.setWidth 64) 1 = 0 := fun w => by
    ext i hi; simp only [dword, BitVec.getElem_extractLsb']; rw [BitVec.getLsbD_append]; simp
  have c : ∀ a b c d : BitVec 32, qword (ofDwords a b c d) 0 = b ++ a := fun a b c d => by
    ext i hi; simp only [qword, ofDwords, BitVec.getElem_extractLsb']
    rw [BitVec.getLsbD_append, BitVec.getElem_append]; split
    · simp [show i < 32 by omega]
    · rw [BitVec.getLsbD_append]
      simp [show i - 32 < 32 by omega, show ¬ i < 32 by omega]
  simp only [XBinOp.eval, a, b, c]

/-- Byte `j` of four dwords. -/
theorem byte_vec4 (w : Nat → BitVec 32) {j : Nat} (hj : j < 16) :
    byte ((w 3 ++ w 2) ++ (w 1 ++ w 0)) j = (w (j / 4)).extractLsb' (8 * (j % 4)) 8 := by
  simp only [byte]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (disch := decide) only [Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, Nat.reduceMod,
    BitVec.extractLsb'_append_eq_of_le, BitVec.extractLsb'_append_eq_of_add_le]

/-- The bytes of `0x80` as a 32-bit word. -/
theorem byte_0x80 : ∀ j < 4, (0x80 : BitVec 32).extractLsb' (8 * j) 8 = if j = 0 then 0x80 else 0 := by decide

/-- The bytes of `0x80` moved into an SSE register. -/
theorem byte_movq0x80 : ∀ j < 16,
    byte ((0 : BitVec 64) ++ (0x80 : BitVec 32).setWidth 64) j = if j = 0 then 0x80 else 0 := by decide +kernel

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- A 32-bit load, keeping the SSE registers. -/
theorem wp_mov32mX {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a)
    (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Upd s s' d ((s.mem.readW a 32).setWidth 64) → s'.xmm = s.xmm → WP isa (.block is) s' Q) :
    WP isa (.block (.mov32 d (.mem m) :: is)) s Q := by
  refine WP.cons (s' := s.setReg d ((s.mem.readW a 32).setWidth 64)) ?_ (k _ (Upd.setReg _ _ _) rfl)
  simp [exec, readSrc32, State.load32, State.setReg32, ha, hin]

/-- A 32-bit immediate, keeping the SSE registers. -/
theorem wp_mov32iX {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (v.setWidth 64) → s'.xmm = s.xmm → WP isa (.block is) s' Q) :
    WP isa (.block (.mov32 d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _) rfl)

end

variable (H : Hash)

/-- Dword `k` of the block, from the digest at `T` in `m`: the digest's
dwords, then `0x80` and zeros. -/
def dwv (m : Mem) (T : Addr) (k : Nat) : BitVec 32 :=
  if k < H.D / 4 then m.readW (T + BitVec.ofNat 64 (4 * k)) 32 else if k = H.D / 4 then 0x80 else 0

/-- Byte `i` of the block before its last 16 bytes. -/
def blkB (m : Mem) (T : Addr) (i : Nat) : Byte :=
  if i < H.D then m (T + BitVec.ofNat 64 i) else if i = H.D then 0x80 else 0

theorem dwv_byte (hD4 : H.D % 4 = 0) (m : Mem) (T : Addr) (i : Nat) :
    (dwv H m T (i / 4)).extractLsb' (8 * (i % 4)) 8 = blkB H m T i := by
  unfold dwv blkB
  by_cases h₁ : i / 4 < H.D / 4
  · have hi : i < H.D := by omega
    simp only [h₁, hi, ↓reduceIte]
    rw [← Mem.readW_byte m _ (Nat.mod_lt _ (by decide)), add_ofNat, show 4 * (i / 4) + i % 4 = i by omega]
  · have hi : ¬ i < H.D := by omega
    by_cases h₂ : i / 4 = H.D / 4
    · rw [ite_f h₁, ite_t h₂, byte_0x80 _ (Nat.mod_lt _ (by decide)), ite_f hi]
      by_cases h₃ : i = H.D
      · rw [ite_t h₃, ite_t (by omega)]
      · rw [ite_f h₃, ite_f (by omega)]
    · have h₃ : ¬ i = H.D := by omega
      simp only [h₁, h₂, hi, h₃, ↓reduceIte]
      exact BitVec.extractLsb'_zero

/-- Dword `k` of the block, into `x`. -/
theorem dw_ok {k : Nat} {x : XReg} {s : State} {T : Addr}
    (hT : s.gpr .r15 + BitVec.ofNat 64 H.stream.buf = T)
    (hin : k < H.D / 4 → InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 (4 * k)) 4)
    {rest : List Instr} {Q : State → Prop}
    (kk : ∀ s', (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.mem = s.mem →
      s'.xmm x = ((0 : BitVec 64) ++ (dwv H s.mem T k).setWidth 64 : BitVec 128) → (∀ y, y ≠ x → s'.xmm y = s.xmm y) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (H.blkDw k ++ .xop (.movq x .rax) :: rest)) s Q := by
  unfold Hash.blkDw
  by_cases h : k < H.D / 4
  · rw [ite_t h, List.singleton_append]
    refine wp_mov32mX (by rw [ea_off, hT]) (hin h) fun s₁ u₁ x₁ => wp_movqx (kk _ ?_ ?_ ?_ ?_ ?_ ?_)
    · intro r hr; rw [gpr_setXmm, u₁.other r hr]
    · rw [rd_setXmm, u₁.rd]
    · rw [wr_setXmm, u₁.wr]
    · rw [mem_setXmm, u₁.mem]
    · rw [xmm_setXmm_self, u₁.gpr, dwv, ite_t h]
    · intro y hy; rw [xmm_setXmm_of_ne _ _ hy, x₁]
  · rw [ite_f h, List.singleton_append]
    refine wp_mov32iX fun s₁ u₁ x₁ => wp_movqx (kk _ ?_ ?_ ?_ ?_ ?_ ?_)
    · intro r hr; rw [gpr_setXmm, u₁.other r hr]
    · rw [rd_setXmm, u₁.rd]
    · rw [wr_setXmm, u₁.wr]
    · rw [mem_setXmm, u₁.mem]
    · rw [xmm_setXmm_self, u₁.gpr, dwv, ite_f h]
    · intro y hy; rw [xmm_setXmm_of_ne _ _ hy, x₁]

theorem ea_rbp (s : State) (o : Nat) : s.ea (at_ .rbp o) = s.gpr .rbp + BitVec.ofNat 64 o := by
  rw [ea_at, ofInt_natCast]

/-- The 16 bytes of the block at `p + 16 c`, before its last 16. -/
theorem chunk_ok {c : Nat} {s : State} {p T : Addr} (hD4 : H.D % 4 = 0)
    (hbp : s.gpr .rbp = p) (hT : s.gpr .r15 + BitVec.ofNat 64 H.stream.buf = T)
    (hin : ∀ k < H.D / 4, InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 (4 * k)) 4)
    (hout : InRegions s.wr (p + BitVec.ofNat 64 (16 * c)) 16) {rest : List Instr} {Q : State → Prop}
    (kk : ∀ s' (v : BitVec 128), (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = s.mem.writeW (p + BitVec.ofNat 64 (16 * c)) v →
      (∀ j < 16, byte v j = blkB H s.mem T (16 * c + j)) → WP isa (.block rest) s' Q) :
    WP isa (.block (H.blkChunk c ++ rest)) s Q := by
  unfold Hash.blkChunk
  by_cases ha : H.D / 4 < 4 * c
  · -- After the `0x80`: zeros.
    rw [ite_t ha]
    simp only [List.cons_append, List.nil_append]
    refine wp_xbin (wp_movdquStore (by rw [ea_rbp, gpr_setXmm, hbp]) (by rw [wr_setXmm]; exact hout)
      fun s₁ g₁ m₁ rd₁ wr₁ => kk s₁ _ (fun r _ => by rw [g₁, gpr_setXmm]) (by rw [rd₁, rd_setXmm])
        (by rw [wr₁, wr_setXmm]) (by rw [m₁, mem_setXmm]) fun j hj => ?_)
    have px : ∀ a : BitVec 128, XBinOp.pxor.eval a a = 0 := fun a => BitVec.xor_self
    have := Nat.div_add_mod H.D 4
    rw [xmm_setXmm_self, px, byte_zero, blkB, ite_f (show ¬ 16 * c + j < H.D by omega),
      ite_f (show ¬ 16 * c + j = H.D by omega)]
  rw [ite_f ha]
  by_cases hb : H.D / 4 = 4 * c
  · -- The `0x80`, then zeros.
    rw [ite_t hb]
    simp only [List.cons_append, List.nil_append]
    refine wp_mov32iX fun s₁ u₁ x₁ => wp_movqx (wp_movdquStore (by rw [ea_rbp, gpr_setXmm, u₁.other _ (by decide), hbp])
      (by rw [wr_setXmm, u₁.wr]; exact hout)
      fun s₂ g₂ m₂ rd₂ wr₂ => kk s₂ _ (fun r hr => by rw [g₂, gpr_setXmm, u₁.other r hr]) (by rw [rd₂, rd_setXmm, u₁.rd])
        (by rw [wr₂, wr_setXmm, u₁.wr]) (by rw [m₂, mem_setXmm, u₁.mem]) fun j hj => ?_)
    have hD : H.D = 16 * c := by have := Nat.div_add_mod H.D 4; omega
    rw [xmm_setXmm_self, u₁.gpr, byte_movq0x80 j hj, blkB, ite_f (show ¬ 16 * c + j < H.D by omega)]
    by_cases hj0 : j = 0
    · rw [ite_t hj0, ite_t (show 16 * c + j = H.D by omega)]
    · rw [ite_f hj0, ite_f (show ¬ 16 * c + j = H.D by omega)]
  · -- Four dwords of the digest, or of the digest and the `0x80`.
    rw [ite_f hb]
    have hin' : ∀ {t : State}, t.rd = s.rd → t.wr = s.wr → ∀ {k : Nat}, k < H.D / 4 →
        InRegions (t.rd ++ t.wr) (T + BitVec.ofNat 64 (4 * k)) 4 := fun h1 h2 k hk => by
      rw [h1, h2]; exact hin k hk
    simp only [List.append_assoc, List.cons_append]
    refine dw_ok H hT (fun hk => hin _ hk) fun s₁ g₁ rd₁ wr₁ m₁ x₁ y₁ => ?_
    refine dw_ok H (by rw [g₁ _ (by decide), hT]) (fun hk => hin' rd₁ wr₁ hk) fun s₂ g₂ rd₂ wr₂ m₂ x₂ y₂ => ?_
    refine dw_ok H (by rw [g₂ _ (by decide), g₁ _ (by decide), hT])
      (fun hk => hin' (rd₂.trans rd₁) (wr₂.trans wr₁) hk) fun s₃ g₃ rd₃ wr₃ m₃ x₃ y₃ => ?_
    refine dw_ok H (by rw [g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hT])
      (fun hk => hin' (rd₃.trans (rd₂.trans rd₁)) (wr₃.trans (wr₂.trans wr₁)) hk) fun s₄ g₄ rd₄ wr₄ m₄ x₄ y₄ => ?_
    refine wp_xbin (wp_xbin (wp_xbin (wp_movdquStore
      (by rw [ea_rbp, gpr_setXmm, gpr_setXmm, gpr_setXmm, g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide),
        g₁ _ (by decide), hbp])
      (by rw [wr_setXmm, wr_setXmm, wr_setXmm, wr₄, wr₃, wr₂, wr₁]; exact hout)
      fun s₅ g₅ m₅ rd₅ wr₅ => ?_)))
    rw [mem_setXmm, mem_setXmm, mem_setXmm, m₄, m₃, m₂, m₁] at m₅
    refine kk s₅ _ ?_ ?_ ?_ m₅ fun j hj => ?_
    · intro r hr; rw [g₅, gpr_setXmm, gpr_setXmm, gpr_setXmm, g₄ r hr, g₃ r hr, g₂ r hr, g₁ r hr]
    · rw [rd₅, rd_setXmm, rd_setXmm, rd_setXmm, rd₄, rd₃, rd₂, rd₁]
    · rw [wr₅, wr_setXmm, wr_setXmm, wr_setXmm, wr₄, wr₃, wr₂, wr₁]
    · rw [m₃, m₂, m₁] at x₄; rw [m₂, m₁] at x₃; rw [m₁] at x₂
      simp (disch := decide) only [xmm_setXmm_self, xmm_setXmm_of_ne]
      rw [x₄, y₄ .xmm2 (by decide), x₃, y₄ .xmm1 (by decide), y₃ .xmm1 (by decide), x₂,
        y₄ .xmm0 (by decide), y₃ .xmm0 (by decide), y₂ .xmm0 (by decide), x₁, vec4]
      have e := byte_vec4 (fun i => dwv H s.mem T (4 * c + i)) hj
      simp only [Nat.add_zero] at e
      rw [e, show 4 * c + j / 4 = (16 * c + j) / 4 by omega, show j % 4 = (16 * c + j) % 4 by omega,
        dwv_byte H hD4]

/-- The first `n` chunks: the block's first `16 n` bytes. -/
theorem chunks_ok {p T : Addr} (hD4 : H.D % 4 = 0) (n : Nat) :
    ∀ (s : State) (rest : List Instr) (Q : State → Prop),
    s.gpr .rbp = p → s.gpr .r15 + BitVec.ofNat 64 H.stream.buf = T →
    (∀ k < H.D / 4, InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ c < n, InRegions s.wr (p + BitVec.ofNat 64 (16 * c)) 16) →
    Region.Disjoint ⟨T, H.D⟩ ⟨p, 16 * n⟩ → H.D < 2 ^ 63 → 16 * n < 2 ^ 63 →
    (∀ s', (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      Frame [⟨p, 16 * n⟩] s.mem s'.mem → (∀ i < 16 * n, s'.mem (p + BitVec.ofNat 64 i) = blkB H s.mem T i) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap H.blkChunk ++ rest)) s Q := by
  induction n with
  | zero =>
    intro s rest Q _ _ _ _ _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl (Frame.refl _ _) fun i hi => by omega
  | succ n ih =>
    intro s rest Q hbp hT hin hout hdis hD hn k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih s _ Q hbp hT hin (fun c hc => hout c (by omega))
      (hdis.sub_right (Region.sub_prefix (by omega))) hD (by omega) fun s₁ g₁ rd₁ wr₁ f₁ b₁ => ?_
    refine chunk_ok H (c := n) hD4 (by rw [g₁ _ (by decide), hbp]) (by rw [g₁ _ (by decide), hT])
      (fun k hk => by rw [rd₁, wr₁]; exact hin k hk) (by rw [wr₁]; exact hout n (by omega))
      fun s₂ v g₂ rd₂ wr₂ m₂ hv => k s₂ (fun r hr => by rw [g₂ r hr, g₁ r hr]) (by rw [rd₂, rd₁])
        (by rw [wr₂, wr₁]) ?_ fun i hi => ?_
    · rw [m₂]
      refine (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW (List.mem_singleton_self _) _ ?_
      · simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)
      · exact Offset.contains_base p (d := 16 * n) (n := 128 / 8) (k := 16 * (n + 1)) (by omega) (by omega)
    · -- The digest is where it was.
      have hT₁ : blkB H s₁.mem T = blkB H s.mem T := by
        funext i
        unfold blkB
        by_cases h : i < H.D
        · rw [ite_t h, ite_t h]
          exact f₁.bytes (R := ⟨T, H.D⟩) (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact hdis.sub_right (Region.sub_prefix (by omega))) (by show H.D ≤ 2 ^ 64; omega) h
        · rw [ite_f h, ite_f h]
      rw [m₂, writeW128_at _ _ _ (by omega) (by omega)]
      split
      · rename_i h
        rw [hv _ (by omega), hT₁, show 16 * n + (i - 16 * n) = i by omega]
      · exact b₁ i (by omega)

/-- `blkV` writes the block at `p` (`rbp`): the `D`-byte digest at `T`
(`scratch + buf`, `r15`), then the padding of a `B + D`-byte message. -/
theorem blkV_ok {M : Md H.P.B H.P.N H.P.L} (hs : Shape M) (hok : M.lenOk (H.P.B + H.D)) (hD4 : H.D % 4 = 0)
    (hB : H.P.B = 64 ∨ H.P.B = 128) (hDB : H.D + 4 ≤ H.P.B - 16) (hL : H.P.L ≤ 16)
    {s : State} {p T : Addr} (hbp : s.gpr .rbp = p) (hT : s.gpr .r15 + BitVec.ofNat 64 H.stream.buf = T)
    (hin : ∀ k < H.D / 4, InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 (4 * k)) 4)
    (hw : ∀ a n, a + n ≤ H.P.B → InRegions s.wr (p + BitVec.ofNat 64 a) n)
    (hdis : Region.Disjoint ⟨T, H.D⟩ ⟨p, H.P.B⟩) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .rax → r ≠ .r12 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      Frame [⟨p, H.P.B⟩] s.mem s'.mem → bytesAt s'.mem p H.D = bytesAt s.mem T H.D →
      bytesAt s'.mem (p + BitVec.ofNat 64 H.D) (H.P.B - H.D) = M.tailPad H.D → WP isa (.block rest) s' Q) :
    WP isa (.block (H.blkV ++ rest)) s Q := by
  have hB' : H.P.B ≤ 128 := by omega
  unfold Hash.blkV
  simp only [List.append_assoc]
  refine chunks_ok H hD4 (H.P.B / 16 - 1) s _ Q hbp hT hin (fun c hc => hw _ _ (by omega))
    (hdis.sub_right (Region.sub_prefix (by omega))) (by omega) (by omega) fun s₁ g₁ rd₁ wr₁ f₁ b₁ => ?_
  simp only [List.cons_append, List.nil_append]
  refine wp_mov32i fun s₂ u₂ _ _ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (hs.lenV s₂) fun s₃ ⟨g₃, rd₃, wr₃, m₃, _, v₃⟩ => ?_
  have hp₃ : s₃.gpr .rbp = p := by rw [g₃ _ (by decide), u₂.other _ (by decide), g₁ _ (by decide), hbp]
  refine wp_movdquStore (by rw [ea_rbp, hp₃]) (by rw [wr₃, u₂.wr, wr₁]; exact hw _ _ (by omega))
    fun s₄ g₄ m₄ rd₄ wr₄ => k s₄ ?_ (by rw [rd₄, rd₃, u₂.rd, rd₁]) (by rw [wr₄, wr₃, u₂.wr, wr₁]) ?_ ?_ ?_
  · intro r h1 h2; rw [g₄, g₃ r h1, u₂.other r h2, g₁ r h1]
  · rw [m₄, m₃, u₂.mem]
    refine (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW (List.mem_singleton_self _) _ ?_
    · simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)
    · exact Offset.contains_base p (d := H.P.B - 16) (n := 128 / 8) (k := H.P.B) (by omega) (by omega)
  · -- Every byte of the block.
    have hby : ∀ i < H.P.B, s₄.mem (p + BitVec.ofNat 64 i) =
        if i < H.P.B - 16 then blkB H s.mem T i else byte (s₃.xmm .xmm7) (i - (H.P.B - 16)) := by
      intro i hi
      rw [m₄, m₃, u₂.mem, writeW128_at _ _ _ (by omega) (by omega)]
      by_cases h : i < H.P.B - 16
      · rw [ite_f (by omega), ite_t h, b₁ i (by omega)]
      · rw [ite_t (by omega), ite_f h]
    simp only [bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    rw [hby i (by omega), ite_t (show i < H.P.B - 16 by omega), blkB, ite_t hi]
  · -- The padding.
    have hby : ∀ i < H.P.B, s₄.mem (p + BitVec.ofNat 64 i) =
        if i < H.P.B - 16 then blkB H s.mem T i else byte (s₃.xmm .xmm7) (i - (H.P.B - 16)) := by
      intro i hi
      rw [m₄, m₃, u₂.mem, writeW128_at _ _ _ (by omega) (by omega)]
      by_cases h : i < H.P.B - 16
      · rw [ite_f (by omega), ite_t h, b₁ i (by omega)]
      · rw [ite_t (by omega), ite_f h]
    have v₃' : vbytes (s₃.xmm .xmm7) = List.replicate (16 - H.P.L) 0 ++ M.lenBytes (H.P.B + H.D) := by
      rw [v₃, u₂.gpr, zx_ofNat (by omega), M.lenOf_eq _ hok]
    have bj : ∀ j < 16, byte (s₃.xmm .xmm7) j =
        (List.replicate (16 - H.P.L) 0 ++ M.lenBytes (H.P.B + H.D)).getD j 0 := by
      intro j hj
      rw [← v₃', ← vbytes_getElem _ (by rw [vbytes_length]; exact hj), List.getElem_eq_getD 0]
    have hLB := M.lenBytes_length (H.P.B + H.D)
    apply List.ext_getElem
    · simp only [bytesAt, List.length_map, List.length_range, Md.tailPad, List.length_append,
        List.length_singleton, List.length_replicate, hLB]
      omega
    intro i h1 h2
    simp only [bytesAt, List.length_map, List.length_range] at h1
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    rw [add_ofNat, hby _ (by omega)]
    simp only [Md.tailPad]
    by_cases h0 : i = 0
    · subst h0
      rw [ite_t (by omega), blkB, ite_f (by omega), ite_t (by omega)]
      simp
    by_cases hz : i < H.P.B - H.P.L - H.D
    · rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
      simp only [List.getElem_replicate]
      by_cases h16 : H.D + i < H.P.B - 16
      · rw [ite_t h16, blkB, ite_f (by omega), ite_f (by omega)]
      · rw [ite_f h16, bj _ (by omega), List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega),
          List.getElem?_replicate_of_lt (by omega)]
        rfl
    · rw [List.getElem_append_right (by simp; omega), ite_f (by omega), bj _ (by omega),
        List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
      simp only [List.length_replicate, List.length_append, List.length_singleton]
      rw [List.getElem?_eq_getElem (by rw [hLB]; omega)]
      simp only [Option.getD_some]
      congr 1; omega

end VG.Proof.Pbkdf2.Md.X86_64.Blk
