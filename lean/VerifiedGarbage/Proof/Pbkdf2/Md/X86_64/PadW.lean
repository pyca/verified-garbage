module

import VerifiedGarbage.Proof.Pbkdf2.X86_64.Iterate
import VerifiedGarbage.Proof.Pbkdf2.Memory
import VerifiedGarbage.Proof.MdStream.X86_64.PadExec
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.Pbkdf2.MdStep
public import VerifiedGarbage.Impl.Pbkdf2.Md.X86_64
public import VerifiedGarbage.Proof.MdStream.X86_64.Common
import VerifiedGarbage.Proof.MdStream.X86_64.Words
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract

/-!
# HMAC over any Merkle–Damgård hash function on x86-64: the outer block's padding

What `Hash.padW` (`Impl/Pbkdf2/Md/X86_64.lean`) writes after the `D`-byte
digest in the outer block: the end of a `B + D`-byte message (`Md.tailPad`),
as `padLen` does (`Proof/Pbkdf2/X86_64/Iterate.lean`, `padLen_ok`), but in
16-byte stores: `0x80` and zeros up to `padA`, zeros, and the last 16 bytes
as the hash function's `lenV` builds them (`Shape.lenV`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.X86_64

open VG.X86_64 VG.Proof.MdStream
open VG.Proof.MdStream.X86_64 (Shape vbytes vbytes_length wp_movqx wp_xbin wp_movdquStore wp_mov32i ea_at
  ofInt_natCast zx_ofNat add_ofNat setWidth32)
open VG.Impl.MdStream.X86_64 (at_)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_frame)
open VG.Proof.Hmac.Common (bytesAt_writeBytes_sep)
open VG.Proof.Hmac.Generic.Common (bytesAt_writeBytes_self')
open Spec.Sha256 (bytesAt)

/-- A 16-byte store writes the bytes of the register. -/
theorem writeW128 (m : Mem) (a : Addr) (v : BitVec 128) : m.writeW a v = writeBytes m a (vbytes v) :=
  Pbkdf2.Memory.writeW_bytes m a v _ (by simp only [Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]; rfl)

/-- `c` 16-byte stores of `xmm0`, zero, from `[rbp + A]`. -/
theorem zst_ok (A : Nat) (c : Nat) :
    ∀ (rest : List Instr) (s : State) (Q : State → Prop) (p : Addr), s.gpr .rbp = p → s.xmm .xmm0 = 0 →
    (∀ k < c, InRegions s.wr (p + BitVec.ofNat 64 (A + 16 * k)) 16) →
    A + 16 * c < 2 ^ 63 →
    (∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.xmm = s.xmm →
      s'.mem = writeBytes s.mem (p + BitVec.ofNat 64 A) (List.replicate (16 * c) 0) → WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range c).map (fun k => Instr.movdquStore (at_ .rbp (A + 16 * k)) .xmm0) ++ rest)) s Q := by
  induction c with
  | zero =>
    intro rest s Q p _ _ _ _ k
    exact k s rfl rfl rfl rfl (by rw [Nat.mul_zero, List.replicate_zero, writeBytes_nil])
  | succ c ih =>
    intro rest s Q p hbp hx hout hlt k
    rw [List.range_succ, List.map_append, List.map_singleton, List.append_assoc]
    refine ih _ s Q p hbp hx (fun j hj => hout j (by omega)) (by omega) fun s₁ g₁ rd₁ wr₁ x₁ m₁ => ?_
    simp only [List.cons_append, List.nil_append]
    refine MdStream.X86_64.wp_movdquStoreX (a := p + BitVec.ofNat 64 (A + 16 * c)) (by rw [ea_at, g₁, hbp, ofInt_natCast])
      (by rw [wr₁]; exact hout c (by omega)) fun s₂ g₂ m₂ rd₂ wr₂ x₂ => k s₂ (by rw [g₂, g₁])
        (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) (by rw [x₂, x₁]) ?_
    rw [m₂, m₁, x₁, hx, writeW128,
      Pbkdf2.Memory.writeBytes_append' _ _ _ (by rw [List.length_replicate, add_ofNat]) (by simp [vbytes_length]; omega),
      show vbytes 0 = List.replicate 16 0 from by decide, List.replicate_append_replicate, Nat.mul_succ]

/-- `padW` writes the rest of the block at `p` (`rbp`) after its first `D`
bytes, which it keeps: the padding of a `B + D`-byte message, as `padLen`. -/
theorem padW_ok {H : Hash} {M : Md H.P.B H.P.N H.P.L} (hs : Shape M) (hok : M.lenOk (H.P.B + H.D))
    (hD4 : H.D % 4 = 0) (hB16 : H.P.B % 16 = 0) (hL : 0 < H.P.L ∧ H.P.L ≤ 16) (hA : H.padA + 16 ≤ H.P.B)
    (hB : H.P.B ≤ 128) {s : State} {p : Addr} (hbp : s.gpr .rbp = p)
    (hw : ∀ a n, a + n ≤ H.P.B → InRegions s.wr (p + BitVec.ofNat 64 a) n) {rest : List Instr}
    {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .rax → r ≠ .r12 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      Frame [⟨p, H.P.B⟩] s.mem s'.mem → bytesAt s'.mem (p + BitVec.ofNat 64 H.D) (H.P.B - H.D) = M.tailPad H.D →
      bytesAt s'.mem p H.D = bytesAt s.mem p H.D → WP isa (.block rest) s' Q) :
    WP isa (.block (H.padW ++ rest)) s Q := by
  have hAD : H.D + 1 ≤ H.padA := by simp only [Hash.padA]; omega_arith
  have hA16 : H.padA % 16 = 0 := by simp only [Hash.padA]; omega_arith
  -- The head: `0x80` and zeros from `D` up to `padA`.
  have head : ∀ (rest' : List Instr),
      (∀ s', (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
        s'.mem = writeBytes s.mem (p + BitVec.ofNat 64 H.D) ([0x80] ++ List.replicate (H.padA - H.D - 1) 0) →
        WP isa (.block rest') s' Q) →
      WP isa (.block ((if H.D % 16 = 0 then
        ([.mov32 .rax (.imm 0x80), .xop (.movq .xmm1 .rax), .movdquStore (at_ .rbp H.D) .xmm1] : List Instr)
        else Impl.Pbkdf2.X86_64.padFrom H.D H.padA) ++ rest')) s Q := by
    intro rest' k'
    split
    · rename_i h16
      have e : H.padA - H.D - 1 = 15 := by simp only [Hash.padA]; omega_arith
      simp only [List.cons_append, List.nil_append]
      refine wp_mov32i fun s₁ u₁ _ _ => wp_movqx ?_
      refine wp_movdquStore (a := p + BitVec.ofNat 64 H.D)
        (by rw [ea_at, RegUpd.gpr_setXmm, u₁.other _ (by decide), hbp, ofInt_natCast])
        (by rw [RegUpd.wr_setXmm, u₁.wr]; exact hw _ _ (by omega_arith)) fun s₂ g₂ m₂ rd₂ wr₂ =>
          k' s₂ (fun r hr => by rw [g₂, RegUpd.gpr_setXmm, u₁.other r hr]) (by rw [rd₂, RegUpd.rd_setXmm, u₁.rd])
            (by rw [wr₂, RegUpd.wr_setXmm, u₁.wr]) ?_
      rw [m₂, RegUpd.mem_setXmm, RegUpd.xmm_setXmm_self, u₁.gpr, u₁.mem, writeW128, e]
      rfl
    · rename_i h16
      exact Pbkdf2.X86_64.padFrom_ok (a := H.D) (b := H.padA) (by simp only [Hash.padA]; omega_arith)
        (by simp only [Hash.padA]; omega_arith) (by omega_arith) hbp (fun j hj => hw _ _ (by simp only [Hash.padA] at hj ⊢; omega_arith))
        fun s' g rd wr m => k' s' g rd wr m
  unfold Hash.padW
  simp only [List.append_assoc, List.cons_append]
  refine head _ fun s₁ g₁ rd₁ wr₁ m₁ => wp_xbin ?_
  have z₀ : (XBinOp.eval .pxor (s₁.xmm .xmm0) (s₁.xmm .xmm0)) = 0 := by
    simp only [XBinOp.eval, BitVec.xor_self]; rfl
  have c16 : H.padA + 16 * ((H.P.B - 16 - H.padA) / 16) = H.P.B - 16 := by omega_arith
  refine zst_ok H.padA ((H.P.B - 16 - H.padA) / 16) _ _ Q p (by rw [RegUpd.gpr_setXmm, g₁ _ (by decide), hbp])
    (by rw [RegUpd.xmm_setXmm_self, z₀]) (fun j hj => by rw [RegUpd.wr_setXmm, wr₁]; exact hw _ _ (by omega_arith))
    (by omega_arith) fun s₂ g₂ rd₂ wr₂ _ m₂ => ?_
  refine wp_mov32i fun s₃ u₃ _ _ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (hs.lenV s₃) fun s₄ ⟨g₄, rd₄, wr₄, mem₄, _, x₄⟩ => ?_
  have r12 : s₃.gpr .r12 = BitVec.ofNat 64 (H.P.B + H.D) := by rw [u₃.gpr, zx_ofNat (by omega_arith)]
  rw [r12, M.lenOf_eq _ hok] at x₄
  have bp₄ : s₄.gpr .rbp = p := by
    rw [g₄ _ (by decide), u₃.other _ (by decide), g₂, RegUpd.gpr_setXmm, g₁ _ (by decide), hbp]
  refine wp_movdquStore (a := p + BitVec.ofNat 64 (H.P.B - 16)) (by rw [ea_at, bp₄, ofInt_natCast])
    (by rw [wr₄, u₃.wr, wr₂, RegUpd.wr_setXmm, wr₁]; exact hw _ _ (by omega_arith)) fun s₅ g₅ m₅ rd₅ wr₅ => ?_
  -- What the block's tail is.
  have hlen : (M.lenBytes (H.P.B + H.D)).length = H.P.L := M.lenBytes_length _
  obtain ⟨tl, htl⟩ : ∃ tl : List Byte, tl = [0x80] ++ List.replicate (H.P.B - H.P.L - 1 - H.D) 0 ++
      M.lenBytes (H.P.B + H.D) := ⟨_, rfl⟩
  have tlen : tl.length = H.P.B - H.D := by
    simp only [htl, List.length_append, List.length_cons, List.length_nil, List.length_replicate, hlen]
    omega_arith
  have hm : s₅.mem = writeBytes s.mem (p + BitVec.ofNat 64 H.D) tl := by
    rw [m₅, writeW128, x₄, mem₄, u₃.mem, m₂, RegUpd.mem_setXmm, m₁,
      Pbkdf2.Memory.writeBytes_append' _ (List.replicate (16 * ((H.P.B - 16 - H.padA) / 16)) 0)
        (List.replicate (16 - H.P.L) 0 ++ M.lenBytes (H.P.B + H.D))
        (by rw [List.length_replicate, add_ofNat, c16]) (by simp [hlen]; omega_arith),
      Pbkdf2.Memory.writeBytes_append' _ ([0x80] ++ List.replicate (H.padA - H.D - 1) 0)
        (List.replicate (16 * ((H.P.B - 16 - H.padA) / 16)) 0 ++ (List.replicate (16 - H.P.L) 0 ++ M.lenBytes (H.P.B + H.D)))
        (by rw [List.length_append, List.length_singleton, List.length_replicate, add_ofNat]; congr 2; omega_arith)
        (by simp [hlen]; omega_arith)]
    rw [htl, ← List.append_assoc (List.replicate _ _), List.replicate_append_replicate, List.append_assoc,
      ← List.append_assoc (List.replicate _ _), List.replicate_append_replicate]
    simp only [List.append_assoc]
    rw [show H.padA - H.D - 1 + (16 * ((H.P.B - 16 - H.padA) / 16) + (16 - H.P.L)) = H.P.B - H.P.L - 1 - H.D by
      omega_arith]
  have sep : Mem.Sep p H.D (p + BitVec.ofNat 64 H.D) (H.P.B - H.D) := by
    have := Offset.sep p (d := 0) (n := H.D) (e := H.D) (k := H.P.B - H.D) (.inl (Nat.le_of_eq (Nat.zero_add _)))
      (by omega_arith) (by omega_arith)
    rwa [BitVec.add_zero] at this
  rw [List.nil_append]
  refine k s₅ (fun r h1 h2 => by
      rw [g₅, g₄ r h1, u₃.other r h2, g₂, RegUpd.gpr_setXmm, g₁ r h1])
    (by rw [rd₅, rd₄, u₃.rd, rd₂, RegUpd.rd_setXmm, rd₁]) (by rw [wr₅, wr₄, u₃.wr, wr₂, RegUpd.wr_setXmm, wr₁])
    (by rw [hm]; exact writeBytes_frame _ _ _ (by rw [tlen]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)))
    (by rw [hm, bytesAt_writeBytes_self' tlen (by omega_arith), htl]; rfl)
    (by rw [hm, bytesAt_writeBytes_sep _ _ (by rw [tlen]; exact sep) (by omega_arith)])

/-- `padSel`: `padW` or `padLen`, which write the same. -/
theorem padSel_ok {H : Hash} {M : Md H.P.B H.P.N H.P.L} (hs : Shape M) (hok : M.lenOk (H.P.B + H.D))
    (hD4 : H.D % 4 = 0) (hB16 : H.P.B % 16 = 0) (hL : 0 < H.P.L ∧ H.P.L ≤ 16) (hL4 : H.P.L % 4 = 0)
    (hA : H.padA + 16 ≤ H.P.B) (hpad : H.D + 4 ≤ H.P.B - H.P.L)
    (hB : H.P.B ≤ 128) {s : State} {p : Addr} (hbp : s.gpr .rbp = p)
    (hbx : s.gpr .rbx + BitVec.ofNat 64 (H.P.N + H.P.B - H.P.L) = p + BitVec.ofNat 64 (H.P.B - H.P.L))
    (hw : ∀ a n, a + n ≤ H.P.B → InRegions s.wr (p + BitVec.ofNat 64 a) n) {rest : List Instr}
    {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .rax → r ≠ .r12 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      Frame [⟨p, H.P.B⟩] s.mem s'.mem → bytesAt s'.mem (p + BitVec.ofNat 64 H.D) (H.P.B - H.D) = M.tailPad H.D →
      bytesAt s'.mem p H.D = bytesAt s.mem p H.D → WP isa (.block rest) s' Q) :
    WP isa (.block (H.padSel ++ rest)) s Q := by
  unfold Hash.padSel
  split
  · exact padW_ok hs hok hD4 hB16 hL hA hB hbp hw k
  · exact Pbkdf2.X86_64.padLen_ok hs hok hD4 hL4 (by omega) hpad hB hbp hbx hw k

end VG.Proof.Pbkdf2.Md.X86_64
