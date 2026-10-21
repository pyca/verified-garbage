module

public import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Layout
public import VerifiedGarbage.Impl.Ed25519.AArch64.PublicKey
public import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Ed25519.Expanded
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # The copy of a cached SHA-512 digest to `frame 192` (AArch64)

`copyWords` copies the eight words at `x1`, the digest `D` in a region the body only reads, to
`x15`, `frame 192`, where hashing the seed leaves its digest. Proven once over `Whole.Ctx`, for
both signing's and the public key's layouts. -/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64.Whole
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.PublicKey

variable {E : Addr} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {R W : List Region}

/-- The digest's 64 bytes at `D`: read only, and outside everything the body writes. -/
structure CopySrc (E : Addr) (R W : List Region) (D : Addr) : Prop where
  mem : (⟨D, 64⟩ : Region) ∈ R
  out : ∀ r ∈ W ++ [FR E, CK E], Region.Disjoint ⟨D, 64⟩ r

structure CopyInv (E : Addr) (g : Reg → BitVec 64) (v : VReg → BitVec 128) (m₀ : Mem)
    (R W : List Region) (D : Addr) (n : Nat) (t : State) : Prop where
  ctx : Ctx E g v m₀ R W t
  x1 : t.gpr .x1 = D
  x15 : t.gpr .x15 = E + BitVec.ofNat 64 192
  words : ∀ j < n, t.mem.readW (E + BitVec.ofNat 64 (192 + 8 * j)) 64 =
    m₀.readW (D + BitVec.ofNat 64 (8 * j)) 64

/-- The digest's words, as on entry. -/
theorem CopySrc.word {D : Addr} (hs : CopySrc E R W D) {t : State} (hc : Ctx E g v m₀ R W t)
    {k : Nat} (hk : k < 8) :
    t.mem.readW (D + BitVec.ofNat 64 (8 * k)) 64 = m₀.readW (D + BitVec.ofNat 64 (8 * k)) 64 :=
  hc.frame.readW (r := ⟨D, 64⟩) (Offset.contains_base D (by omega) (by omega)) hs.out (by decide)

theorem copyWord_ok {D : Addr} (hs : CopySrc E R W D) {k : Nat} (hk : k < 8) {t : State}
    (hi : CopyInv E g v m₀ R W D k t) :
    WP isa (.block [.ldr .x .x9 .x1 (8 * k), .str .x .x9 .x15 (8 * k)]) t
      (CopyInv E g v m₀ R W D (k + 1)) := by
  have hc := hi.ctx
  have src : InRegions (t.rd ++ t.wr) (t.gpr .x1 + BitVec.ofNat 64 (8 * k)) 8 := by
    rw [hi.x1, hc.rd]
    exact ⟨_, List.mem_append_left _ hs.mem, Offset.contains_base D (by omega) (by omega)⟩
  have dst : InRegions t.wr (E + BitVec.ofNat 64 (192 + 8 * k)) 8 :=
    hc.writable_frame (Offset.contains_base E (by omega) (by omega))
  apply WP.of_runBlock
  rw [runBlock_cons, exec_ldr_x ⟨by omega, by omega⟩ src, runStep_some, runBlock_cons,
    exec_str_x ⟨by omega, by omega⟩ (by
      simpa only [RegUpd.wr_write, RegUpd.gpr_write, reduceCtorEq, ite_false, hi.x15,
        Offset.add_add] using dst),
    runStep_some, runBlock_nil]
  simp only [Option.some.injEq, exists_eq_left', RegUpd.gpr_write, reduceCtorEq, ite_false,
    ite_true, hi.x15, hi.x1, Offset.add_add, RegUpd.mem_write, BitVec.setWidth_eq]
  have hf : Frame [⟨E + BitVec.ofNat 64 (192 + 8 * k), 8⟩] t.mem
      (t.mem.writeW (E + BitVec.ofNat 64 (192 + 8 * k))
        (t.mem.readW (D + BitVec.ofNat 64 (8 * k)) 64)) :=
    (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
  refine ⟨hc.of_frame rfl rfl rfl (fun r hr _ => ?_) (fun _ _ => rfl) hf ?_, ?_, ?_, ?_⟩
  · rw [RegUpd.gpr_write_of_ne]
    rintro rfl; simp [preserved] at hr
  · intro r hr
    rw [List.mem_singleton.mp hr]
    exact .inl (Offset.sub_base _ (by omega))
  · exact (RegUpd.gpr_write_of_ne (s := t) .x (r := .x9) (r' := .x1)
      (t.mem.readW (D + BitVec.ofNat 64 (8 * k)) 64) (by decide)).trans hi.x1
  · exact (RegUpd.gpr_write_of_ne (s := t) .x (r := .x9) (r' := .x15)
      (t.mem.readW (D + BitVec.ofNat 64 (8 * k)) 64) (by decide)).trans hi.x15
  · intro j hj
    by_cases hjk : j = k
    · subst j
      rw [Mem.readW_writeW_self64]
      exact hs.word hc hk
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
      exact hi.words j (by omega)

theorem copyWords_ok {D : Addr} (hs : CopySrc E R W D) :
    ∀ n ≤ 8, ∀ {t : State}, CopyInv E g v m₀ R W D 0 t →
      WP isa (.block ((List.range n).flatMap fun k => [.ldr .x .x9 .x1 (8 * k), .str .x .x9 .x15 (8 * k)]))
        t (CopyInv E g v m₀ R W D n)
  | 0, _, _, h => WP.block_nil h
  | n + 1, hn, _, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    exact WP.mono (copyWords_ok hs n (by omega) h) fun _ hu => copyWord_ok hs (by omega) hu

/-- After the copy, the 64 bytes at `frame 192` are the digest's. -/
theorem copy_digest {D : Addr} (hs : CopySrc E R W D) {t : State} (h0 : CopyInv E g v m₀ R W D 0 t) :
    WP isa (.block copyWords) t fun u => Ctx E g v m₀ R W u ∧
      Spec.Ed25519.bytesAt u.mem (E + 192) 64 = Spec.Ed25519.bytesAt m₀ D 64 :=
  WP.mono (copyWords_ok hs 8 (Nat.le_refl _) h0) fun u hu => ⟨hu.ctx, by
    change Spec.Sha512.bytesAt u.mem (E + BitVec.ofNat 64 192) 64 = _
    refine Proof.Ed25519.bytesAt_of_words fun k hk => ?_
    rw [Offset.add_add]
    exact hu.words k hk⟩

end VG.Proof.Ed25519.AArch64.Whole
