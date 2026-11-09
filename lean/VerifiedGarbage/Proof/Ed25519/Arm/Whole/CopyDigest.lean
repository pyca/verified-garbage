module

public import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Layout
public import VerifiedGarbage.Impl.Ed25519.Arm.PublicKey
public import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # The copy of a cached SHA-512 digest to `frame 184` (Arm)

`copyWords` copies the sixteen words at `r1`, the digest `D` in a region the body only reads, to
`r2`, `frame 184`, where hashing the seed leaves its digest. Proven once over `Whole.Ctx`, for
both signing's and the public key's layouts. -/

@[expose] public section

namespace VG.Proof.Ed25519.Arm.Whole
open VG VG.Arm VG.Impl.Ed25519.Arm.PublicKey

variable {E : BitVec 32} {g : Reg → BitVec 32} {m₀ : Mem} {R W : List Region}

/-- The digest's 64 bytes at `D`: read only, outside everything the body writes, and not
wrapping; and a frame that does not wrap. -/
structure CopySrc (E : BitVec 32) (R W : List Region) (D : BitVec 32) : Prop where
  mem : (⟨State.addr D, 64⟩ : Region) ∈ R
  out : ∀ r ∈ W ++ [FR E], Region.Disjoint ⟨State.addr D, 64⟩ r
  fit : D.toNat + 64 ≤ 2 ^ 32
  top : E.toNat + 248 ≤ 2 ^ 32

structure CopyInv (E : BitVec 32) (g : Reg → BitVec 32) (m₀ : Mem)
    (R W : List Region) (D : BitVec 32) (n : Nat) (t : State) : Prop where
  ctx : Ctx E g m₀ R W t
  r1 : t.gpr .r1 = D
  r2 : t.gpr .r2 = E + BitVec.ofNat 32 184
  words : ∀ j < n, t.mem.readW (State.addr E + BitVec.ofNat 64 (184 + 4 * j)) 32 =
    m₀.readW (State.addr D + BitVec.ofNat 64 (4 * j)) 32

/-- The digest's words, as on entry. -/
theorem CopySrc.word {D : BitVec 32} (hs : CopySrc E R W D) {t : State} (hc : Ctx E g m₀ R W t)
    {k : Nat} (hk : k < 16) :
    t.mem.readW (State.addr D + BitVec.ofNat 64 (4 * k)) 32 =
      m₀.readW (State.addr D + BitVec.ofNat 64 (4 * k)) 32 :=
  hc.frame.readW (r := ⟨State.addr D, 64⟩) (Offset.contains_base _ (by omega) (by omega))
    hs.out (by decide)

theorem copyWord_ok {D : BitVec 32} (hs : CopySrc E R W D) {k : Nat} (hk : k < 16) {t : State}
    (hi : CopyInv E g m₀ R W D k t) :
    WP isa (.block [.ldr .r0 .r1 (4 * k), .str .r0 .r2 (4 * k)]) t
      (CopyInv E g m₀ R W D (k + 1)) := by
  have hc := hi.ctx
  have fd := hs.fit
  have fe := hs.top
  have as : State.addr (D + BitVec.ofNat 32 (4 * k)) = State.addr D + BitVec.ofNat 64 (4 * k) :=
    addr_add (by omega)
  have ad : State.addr (E + BitVec.ofNat 32 184 + BitVec.ofNat 32 (4 * k)) =
      State.addr E + BitVec.ofNat 64 (184 + 4 * k) := by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact addr_add (by omega)
  have src : InRegions (t.rd ++ t.wr) (State.addr (t.gpr .r1 + BitVec.ofNat 32 (4 * k))) 4 := by
    rw [hi.r1, as, hc.rd]
    exact ⟨_, List.mem_append_left _ hs.mem, Offset.contains_base _ (by omega) (by omega)⟩
  have dst : InRegions t.wr (State.addr E + BitVec.ofNat 64 (184 + 4 * k)) 4 :=
    hc.writable_frame (Offset.contains_base _ (by omega) (by omega))
  apply WP.of_runBlock
  rw [runBlock_cons, exec_ldr (by omega) src, runStep_some, runBlock_cons,
    exec_str (by omega) (by
      simpa only [RegUpd.wr_setReg, RegUpd.gpr_setReg_of_ne _ _ (by decide : ¬ Reg.r2 = .r0), hi.r2,
        ad] using dst),
    runStep_some, runBlock_nil]
  simp only [Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_of_ne _ _ (by decide : ¬ Reg.r2 = .r0),
    RegUpd.gpr_setReg_self, RegUpd.mem_setReg, hi.r2, hi.r1, as, ad]
  have hf : Frame [⟨State.addr E + BitVec.ofNat 64 (184 + 4 * k), 4⟩] t.mem
      (t.mem.writeW (State.addr E + BitVec.ofNat 64 (184 + 4 * k))
        (t.mem.readW (State.addr D + BitVec.ofNat 64 (4 * k)) 32)) :=
    (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
  refine ⟨hc.of_frame rfl rfl rfl (fun r hr _ => ?_) hf ?_, ?_, ?_, ?_⟩
  · rw [RegUpd.gpr_setReg_of_ne]
    rintro rfl; simp [preserved] at hr
  · intro r hr
    rw [List.mem_singleton.mp hr]
    exact .inl (Offset.sub_base _ (by omega))
  · exact (RegUpd.gpr_setReg_of_ne t (r := .r0) (r' := .r1) (t.mem.readW (State.addr D + BitVec.ofNat 64 (4 * k)) 32) (by decide)).trans hi.r1
  · exact (RegUpd.gpr_setReg_of_ne t (r := .r0) (r' := .r2) (t.mem.readW (State.addr D + BitVec.ofNat 64 (4 * k)) 32) (by decide)).trans hi.r2
  · intro j hj
    by_cases hjk : j = k
    · subst j
      rw [Mem.readW_writeW_self32]
      exact hs.word hc hk
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
      exact hi.words j (by omega)

theorem copyWords_ok {D : BitVec 32} (hs : CopySrc E R W D) :
    ∀ n ≤ 16, ∀ {t : State}, CopyInv E g m₀ R W D 0 t →
      WP isa (.block ((List.range n).flatMap fun k => [.ldr .r0 .r1 (4 * k), .str .r0 .r2 (4 * k)]))
        t (CopyInv E g m₀ R W D n)
  | 0, _, _, h => WP.block_nil h
  | n + 1, hn, _, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    exact WP.mono (copyWords_ok hs n (by omega) h) fun _ hu => copyWord_ok hs (by omega) hu

/-- 64 bytes from their sixteen little-endian 32-bit words. -/
theorem bytesAt_of_words32 {m m' : Mem} {p p' : Addr}
    (h : ∀ k < 16, m'.readW (p' + BitVec.ofNat 64 (4 * k)) 32 = m.readW (p + BitVec.ofNat 64 (4 * k)) 32) :
    Spec.Ed25519.bytesAt m' p' 64 = Spec.Ed25519.bytesAt m p 64 := by
  unfold Spec.Ed25519.bytesAt
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  have ha : ∀ q : Addr, q + BitVec.ofNat 64 i =
      q + BitVec.ofNat 64 (4 * (i / 4)) + BitVec.ofNat 64 (i % 4) := by
    intro q
    rw [Offset.add_add]
    exact congrArg (fun n => q + BitVec.ofNat 64 n) (by omega)
  rw [ha p', ha p, Mem.readW_byte m' _ (Nat.mod_lt _ (by decide)),
    Mem.readW_byte m _ (Nat.mod_lt _ (by decide)), h _ (by omega)]

/-- After the copy, the 64 bytes at `frame 184` are the digest's. -/
theorem copy_digest {D : BitVec 32} (hs : CopySrc E R W D) {t : State}
    (h0 : CopyInv E g m₀ R W D 0 t) :
    WP isa (.block copyWords) t fun u => Ctx E g m₀ R W u ∧
      Spec.Ed25519.bytesAt u.mem (State.addr E + 184) 64 =
        Spec.Ed25519.bytesAt m₀ (State.addr D) 64 :=
  WP.mono (copyWords_ok hs 16 (Nat.le_refl _) h0) fun u hu => ⟨hu.ctx, by
    change Spec.Ed25519.bytesAt u.mem (State.addr E + BitVec.ofNat 64 184) 64 = _
    refine bytesAt_of_words32 fun k hk => ?_
    rw [Offset.add_add]
    exact hu.words k hk⟩

end VG.Proof.Ed25519.Arm.Whole
